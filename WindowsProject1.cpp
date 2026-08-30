#include <windows.h>
#include <d3d11.h>
#include <dxgi1_6.h>        // 若编译失败可改为 dxgi1_4.h
#include <comdef.h>
#include <shellscalingapi.h>
#include <shellapi.h>
#include <commctrl.h>
#include <vector>
#include <string>
#include <cmath>
#include <cstdint>
#include <cstdio>

// 手动定义缺失的 DXGI 错误码（若 SDK 未提供）
#ifndef DXGI_ERROR_MODE_CHANGE
#define DXGI_ERROR_MODE_CHANGE ((HRESULT)0x887A0027L)
#endif
#ifndef DXGI_ERROR_ACCESS_LOST
#define DXGI_ERROR_ACCESS_LOST ((HRESULT)0x887A0026L)
#endif
#ifndef DXGI_ERROR_INVALID_CALL
#define DXGI_ERROR_INVALID_CALL ((HRESULT)0x887A0001L)
#endif

#pragma comment(lib, "d3d11.lib")
#pragma comment(lib, "dxgi.lib")
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "shcore.lib")

#define WM_TRAYICON (WM_USER + 100)
#define HOTKEY_SCREENSHOT 1
#define HOTKEY_QUIT       2
#define MENU_EXIT         1001

// ========== HDR 处理参数 ==========
// DXGI 在 HDR 模式下输出 scRGB 线性值（Rec.709 原色，无伽马），
// 1.0 对应 SDR 参考白。因此只需：白点归一化 → sRGB 编码 → 裁剪到 [0,1]，
// 不做任何按帧自适应曝光 / 色调映射，即可与 SDR 截图观感一致。
#define HDR_MODE_CHANGE_GRACE_MS 15000  // 模式切换后多久内的全黑帧视为过渡黑帧

// ========== 色彩处理函数 ==========

// 半精度浮点转换（使用 union 避免严格别名问题）
inline float HalfToFloat(uint16_t half) {
    union {
        uint32_t u;
        float f;
    } conv;
    uint32_t sign = (half >> 15) & 0x1;
    uint32_t exponent = (half >> 10) & 0x1F;
    uint32_t mantissa = half & 0x3FF;

    if (exponent == 0) {
        if (mantissa == 0) {
            conv.u = sign << 31;
        }
        else {
            exponent = 1;
            while ((mantissa & 0x400) == 0) {
                mantissa <<= 1;
                exponent--;
            }
            mantissa &= 0x3FF;
            conv.u = (sign << 31) | ((exponent + 127 - 15) << 23) | (mantissa << 13);
        }
    }
    else if (exponent == 0x1F) {
        conv.u = (sign << 31) | 0x7F800000 | (mantissa << 13);
    }
    else {
        conv.u = (sign << 31) | ((exponent + 127 - 15) << 23) | (mantissa << 13);
    }
    return conv.f;
}

// sRGB OETF：线性光 → sRGB 编码（内部已钳制到 [0,1]，超过 1 的 HDR 高光裁剪为白）
inline float LinearToSRGB(float x) {
    x = max(0.0f, min(1.0f, x));
    if (x <= 0.0031308f)
        return x * 12.92f;
    else
        return 1.055f * powf(x, 1.0f / 2.4f) - 0.055f;
}

// sRGB 逆 OETF：sRGB 编码 → 线性光
inline float SRGBToLinear(float x) {
    x = max(0.0f, min(1.0f, x));
    if (x <= 0.04045f)
        return x / 12.92f;
    else
        return powf((x + 0.055f) / 1.055f, 2.4f);
}

// 清理非法值（保留负数，只处理 NaN 和极端值）
inline float SanitizeFloat(float x) {
    if (x != x) return 0.0f;          // NaN -> 0
    if (x > 100.0f) return 100.0f;    // 防止无穷大
    return x;                         // 保留负数
}

// ========== 全局变量 ==========
ID3D11Device* g_pD3DDevice = nullptr;
ID3D11DeviceContext* g_pImmediateContext = nullptr;
IDXGIOutputDuplication* g_pDeskDupl = nullptr;
int g_ScreenWidth = 0;
int g_ScreenHeight = 0;
bool g_bNeedReinitDXGI = false;

// 显示模式状态：HDR 开关 / 分辨率变化时用于检测并重建捕获
DXGI_COLOR_SPACE_TYPE g_LastColorSpace = DXGI_COLOR_SPACE_RGB_FULL_G22_NONE_P709; // SDR
float g_SdrWhiteScale = 1.0f;          // 系统"SDR 内容亮度"滑块相对 80 nits 的倍率
DWORD g_LastModeChangeTick = 0;        // 最近一次模式切换/捕获异常的时间

NOTIFYICONDATA m_nid = {};
HMENU g_hPopupMenu = nullptr;
HWND g_hMainWnd = nullptr;

// ---------- 托盘气泡提示 ----------
void ShowBalloonTip(LPCWSTR szTitle, LPCWSTR szMsg) {
    m_nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP | NIF_INFO;
    wcscpy_s(m_nid.szInfoTitle, _countof(m_nid.szInfoTitle), szTitle);
    wcscpy_s(m_nid.szInfo, _countof(m_nid.szInfo), szMsg);
    m_nid.dwInfoFlags = NIIF_INFO;
    Shell_NotifyIcon(NIM_MODIFY, &m_nid);
}

// ---------- 带重试打开剪贴板 ----------
bool RetryOpenClipboard(HWND hWnd, int maxRetries = 5) {
    for (int i = 0; i < maxRetries; i++) {
        if (OpenClipboard(hWnd))
            return true;
        Sleep(10);
    }
    return false;
}

// ---------- 查询指定显示器当前的 SDR 白亮度倍率（受系统"SDR 内容亮度"滑块影响） ----------
float GetSdrWhiteScale(HMONITOR hMonitor) {
    MONITORINFOEXW mi = {};
    mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(hMonitor, &mi))
        return 1.0f;

    UINT32 pathCount = 0, modeCount = 0;
    if (GetDisplayConfigBufferSizes(QDC_ONLY_ACTIVE_PATHS, &pathCount, &modeCount) != ERROR_SUCCESS)
        return 1.0f;
    std::vector<DISPLAYCONFIG_PATH_INFO> paths(pathCount);
    std::vector<DISPLAYCONFIG_MODE_INFO> modes(modeCount);
    if (QueryDisplayConfig(QDC_ONLY_ACTIVE_PATHS, &pathCount, paths.data(), &modeCount, modes.data(), nullptr) != ERROR_SUCCESS)
        return 1.0f;

    for (UINT32 i = 0; i < pathCount; i++) {
        DISPLAYCONFIG_SOURCE_DEVICE_NAME src = {};
        src.header.type = DISPLAYCONFIG_DEVICE_INFO_GET_SOURCE_NAME;
        src.header.size = sizeof(src);
        src.header.adapterId = paths[i].sourceInfo.adapterId;
        src.header.id = paths[i].sourceInfo.id;
        if (DisplayConfigGetDeviceInfo(&src.header) != ERROR_SUCCESS)
            continue;
        if (wcscmp(src.viewGdiDeviceName, mi.szDevice) != 0)
            continue;

        // 实测（Win11 2026）：SDRWhiteLevel 单位为 1/1000 个 80 nits，即 1000 = 80 nits。
        // 本机 HDR 开启时报告 3000 = 240 nits，与帧内 SDR 白的 scRGB 值 3.0 精确吻合。
        DISPLAYCONFIG_SDR_WHITE_LEVEL wl = {};
        wl.header.type = DISPLAYCONFIG_DEVICE_INFO_GET_SDR_WHITE_LEVEL;
        wl.header.size = sizeof(wl);
        wl.header.adapterId = paths[i].targetInfo.adapterId;
        wl.header.id = paths[i].targetInfo.id;
        if (DisplayConfigGetDeviceInfo(&wl.header) != ERROR_SUCCESS)
            continue;
        float scale = wl.SDRWhiteLevel / 1000.0f;
        if (scale < 1.0f || scale > 6.5f) {
            // 兼容另一种单位约定（1/1000 nits，80000 = 80 nits）
            scale = wl.SDRWhiteLevel / 80000.0f;
        }
        if (scale < 1.0f || scale > 6.5f) scale = 1.0f;
        return scale;
    }
    return 1.0f;
}

// ---------- 初始化DXGI（bSilent=true 时不弹窗，用于后台恢复） ----------
bool InitDXGICapture(bool bSilent = false) {
    // 清理旧资源
    if (g_pDeskDupl) { g_pDeskDupl->Release(); g_pDeskDupl = nullptr; }
    if (g_pImmediateContext) { g_pImmediateContext->Release(); g_pImmediateContext = nullptr; }
    if (g_pD3DDevice) { g_pD3DDevice->Release(); g_pD3DDevice = nullptr; }

    D3D_FEATURE_LEVEL featureLevels[] = { D3D_FEATURE_LEVEL_11_0 };
    HRESULT hr = D3D11CreateDevice(
        nullptr,
        D3D_DRIVER_TYPE_HARDWARE,
        nullptr,
        D3D11_CREATE_DEVICE_BGRA_SUPPORT,
        featureLevels,
        ARRAYSIZE(featureLevels),
        D3D11_SDK_VERSION,
        &g_pD3DDevice,
        nullptr,
        &g_pImmediateContext
    );
    if (FAILED(hr)) {
        if (!bSilent) MessageBox(nullptr, L"D3D11CreateDevice 失败！", L"初始化错误", MB_OK);
        return false;
    }

    IDXGIDevice* pDXGIDevice = nullptr;
    hr = g_pD3DDevice->QueryInterface(__uuidof(IDXGIDevice), (void**)&pDXGIDevice);
    if (FAILED(hr)) {
        if (!bSilent) MessageBox(nullptr, L"QueryInterface(IDXGIDevice) 失败！", L"初始化错误", MB_OK);
        return false;
    }

    IDXGIAdapter* pAdapter = nullptr;
    hr = pDXGIDevice->GetAdapter(&pAdapter);
    pDXGIDevice->Release();
    if (FAILED(hr)) {
        if (!bSilent) MessageBox(nullptr, L"GetAdapter 失败！", L"初始化错误", MB_OK);
        return false;
    }

    IDXGIOutput* pOutput = nullptr;
    hr = pAdapter->EnumOutputs(0, &pOutput);
    pAdapter->Release();
    if (FAILED(hr)) {
        if (!bSilent) MessageBox(nullptr, L"EnumOutputs 失败！", L"初始化错误", MB_OK);
        return false;
    }

    IDXGIOutput1* pOutput1 = nullptr;
    hr = pOutput->QueryInterface(__uuidof(IDXGIOutput1), (void**)&pOutput1);
    if (FAILED(hr)) {
        pOutput->Release();
        if (!bSilent) MessageBox(nullptr, L"QueryInterface(Output1) 失败！", L"初始化错误", MB_OK);
        return false;
    }

    DXGI_OUTPUT_DESC desc;
    pOutput1->GetDesc(&desc);
    g_ScreenWidth = desc.DesktopCoordinates.right - desc.DesktopCoordinates.left;
    g_ScreenHeight = desc.DesktopCoordinates.bottom - desc.DesktopCoordinates.top;

    // 记录当前色彩空间（HDR 开关会改变它）与 SDR 白亮度倍率
    IDXGIOutput6* pOutput6 = nullptr;
    if (SUCCEEDED(pOutput->QueryInterface(__uuidof(IDXGIOutput6), (void**)&pOutput6))) {
        DXGI_OUTPUT_DESC1 desc1;
        if (SUCCEEDED(pOutput6->GetDesc1(&desc1))) {
            g_LastColorSpace = desc1.ColorSpace;
            g_SdrWhiteScale = GetSdrWhiteScale(desc1.Monitor);
        }
        pOutput6->Release();
    }
    pOutput->Release();

    // 显式请求 FP16 帧格式：HDR 桌面下普通 DuplicateOutput 可能交付 8-bit 帧，
    // 而 8-bit 帧在 80 nit 以上已裁剪，无法正确还原亮部。
    // DuplicateOutput1 允许指定格式列表，优先 R16G16B16A16_FLOAT（scRGB 线性）。
    bool bDupl = false;
    IDXGIOutput5* pOutput5 = nullptr;
    if (SUCCEEDED(pOutput1->QueryInterface(__uuidof(IDXGIOutput5), (void**)&pOutput5))) {
        DXGI_FORMAT formats[2] = { DXGI_FORMAT_R16G16B16A16_FLOAT, DXGI_FORMAT_B8G8R8A8_UNORM };
        hr = pOutput5->DuplicateOutput1(g_pD3DDevice, 0, ARRAYSIZE(formats), formats, &g_pDeskDupl);
        pOutput5->Release();
        if (SUCCEEDED(hr)) bDupl = true;
    }
    if (!bDupl) {
        hr = pOutput1->DuplicateOutput(g_pD3DDevice, &g_pDeskDupl);
    }
    pOutput1->Release();
    if (FAILED(hr)) {
        wchar_t dbg[128];
        swprintf_s(dbg, L"QuickSnap: DuplicateOutput 失败 hr=0x%08X\n", (unsigned)hr);
        OutputDebugString(dbg);
        if (!bSilent) MessageBox(nullptr, L"DuplicateOutput 失败！需要 Win8.1+ 显卡支持", L"初始化错误", MB_OK);
        return false;
    }

    g_bNeedReinitDXGI = false;
    return true;
}

// ---------- 检测显示模式（HDR 开关 / 分辨率）是否变化 ----------
bool CheckOutputChanged() {
    if (!g_pD3DDevice) return false;

    IDXGIDevice* pDXGIDevice = nullptr;
    if (FAILED(g_pD3DDevice->QueryInterface(__uuidof(IDXGIDevice), (void**)&pDXGIDevice)))
        return false;
    IDXGIAdapter* pAdapter = nullptr;
    if (FAILED(pDXGIDevice->GetAdapter(&pAdapter))) {
        pDXGIDevice->Release();
        return false;
    }
    pDXGIDevice->Release();

    IDXGIOutput* pOutput = nullptr;
    bool changed = false;
    if (SUCCEEDED(pAdapter->EnumOutputs(0, &pOutput))) {
        IDXGIOutput6* pOutput6 = nullptr;
        if (SUCCEEDED(pOutput->QueryInterface(__uuidof(IDXGIOutput6), (void**)&pOutput6))) {
            DXGI_OUTPUT_DESC1 desc1;
            if (SUCCEEDED(pOutput6->GetDesc1(&desc1))) {
                int w = desc1.DesktopCoordinates.right - desc1.DesktopCoordinates.left;
                int h = desc1.DesktopCoordinates.bottom - desc1.DesktopCoordinates.top;
                if (desc1.ColorSpace != g_LastColorSpace || w != g_ScreenWidth || h != g_ScreenHeight) {
                    g_LastColorSpace = desc1.ColorSpace;
                    g_ScreenWidth = w;
                    g_ScreenHeight = h;
                    g_SdrWhiteScale = GetSdrWhiteScale(desc1.Monitor);
                    changed = true;
                }
            }
            pOutput6->Release();
        }
        pOutput->Release();
    }
    pAdapter->Release();
    return changed;
}

// ---------- 单次捕获：成功返回 S_OK 并输出 HBITMAP ----------
// 返回 DXGI_ERROR_WAIT_TIMEOUT 表示屏幕无更新（不算失败）；
// 其它失败表示 duplication 已失效，需要重建后重试。
HRESULT TryCaptureOnce(bool& isBlackOut, HBITMAP& hOutBitmap) {
    isBlackOut = false;
    hOutBitmap = nullptr;
    if (!g_pDeskDupl) return E_POINTER;

    IDXGIResource* pDesktopResource = nullptr;
    DXGI_OUTDUPL_FRAME_INFO frameInfo;
    HRESULT hr = g_pDeskDupl->AcquireNextFrame(100, &frameInfo, &pDesktopResource);

    if (hr == DXGI_ERROR_WAIT_TIMEOUT) return hr;
    if (hr == DXGI_ERROR_MODE_CHANGE || hr == DXGI_ERROR_ACCESS_LOST || hr == DXGI_ERROR_INVALID_CALL) {
        OutputDebugString(L"QuickSnap: 模式改变或设备丢失，标记重初始化\n");
        return hr;
    }
    if (FAILED(hr) || !pDesktopResource) {
        OutputDebugString(L"QuickSnap: AcquireNextFrame 失败\n");
        return FAILED(hr) ? hr : E_FAIL;
    }

    ID3D11Texture2D* pAcquiredTexture = nullptr;
    hr = pDesktopResource->QueryInterface(__uuidof(ID3D11Texture2D), (void**)&pAcquiredTexture);
    pDesktopResource->Release();
    if (FAILED(hr)) {
        g_pDeskDupl->ReleaseFrame();
        OutputDebugString(L"QuickSnap: QueryInterface 纹理失败\n");
        return E_FAIL;
    }

    D3D11_TEXTURE2D_DESC texDesc;
    pAcquiredTexture->GetDesc(&texDesc);
    int w = static_cast<int>(texDesc.Width);
    int h = static_cast<int>(texDesc.Height);

    // 创建 Staging 纹理
    D3D11_TEXTURE2D_DESC stagingDesc = texDesc;
    stagingDesc.Usage = D3D11_USAGE_STAGING;
    stagingDesc.BindFlags = 0;
    stagingDesc.CPUAccessFlags = D3D11_CPU_ACCESS_READ;
    stagingDesc.MiscFlags = 0;
    stagingDesc.SampleDesc.Count = 1;

    ID3D11Texture2D* pStaging = nullptr;
    hr = g_pD3DDevice->CreateTexture2D(&stagingDesc, nullptr, &pStaging);
    if (FAILED(hr)) {
        pAcquiredTexture->Release();
        g_pDeskDupl->ReleaseFrame();
        OutputDebugString(L"QuickSnap: 创建 Staging 纹理失败\n");
        return E_FAIL;
    }

    g_pImmediateContext->CopyResource(pStaging, pAcquiredTexture);
    pAcquiredTexture->Release();

    D3D11_MAPPED_SUBRESOURCE mapped;
    hr = g_pImmediateContext->Map(pStaging, 0, D3D11_MAP_READ, 0, &mapped);
    if (FAILED(hr)) {
        pStaging->Release();
        g_pDeskDupl->ReleaseFrame();
        OutputDebugString(L"QuickSnap: Map 失败\n");
        return E_FAIL;
    }

    HBITMAP hBitmap = nullptr;
    HDC hdc = GetDC(nullptr);
    std::vector<BYTE> bgraBuffer(w * h * 4);
    bool isBlack = true;

    // 仅 16/32-bit FLOAT 格式视为 HDR（scRGB 线性），R10G10B10A2_UNORM 属于 SDR
    bool isHDR = (texDesc.Format == DXGI_FORMAT_R16G16B16A16_FLOAT ||
        texDesc.Format == DXGI_FORMAT_R32G32B32A32_FLOAT);

    // HDR 桌面判定：实测发现 HDR 模式下 DWM 可能交付两种帧，数值尺度相同（原始 scRGB，
    // SDR 白 = SDRWhiteLevel/80，本机为 3.0），仅编码不同：
    //   FP16/FP32 帧：线性值本身
    //   BGRA8 帧   ：OETF(原始 scRGB)，即已做 sRGB 编码但未做白亮度归一化
    // SDR 桌面的 BGRA8 帧则是标准 display-referred sRGB（直拷贝即可）。
    bool hdrDesktop = (g_LastColorSpace != DXGI_COLOR_SPACE_RGB_FULL_G22_NONE_P709);

    // SDR 白亮度倍率：把系统"SDR 内容亮度"滑块设置归一化回 1.0 = SDR 白
    float whiteScale = (g_SdrWhiteScale >= 0.25f) ? g_SdrWhiteScale : 1.0f;

    for (int y = 0; y < h; y++) {
        BYTE* pSrcRow = reinterpret_cast<BYTE*>(mapped.pData) + y * mapped.RowPitch;
        BYTE* pDstRow = bgraBuffer.data() + y * w * 4;
        for (int x = 0; x < w; x++) {
            float r, g, b;
            BYTE cb = 0, cg = 0, cbb = 0;
            if (isHDR) {
                if (texDesc.Format == DXGI_FORMAT_R16G16B16A16_FLOAT) {
                    uint16_t* pHalf = reinterpret_cast<uint16_t*>(pSrcRow + x * 8);
                    r = HalfToFloat(pHalf[0]);
                    g = HalfToFloat(pHalf[1]);
                    b = HalfToFloat(pHalf[2]);
                }
                else { // R32G32B32A32_FLOAT
                    float* pFloat = reinterpret_cast<float*>(pSrcRow + x * 16);
                    r = pFloat[0];
                    g = pFloat[1];
                    b = pFloat[2];
                }
                r = SanitizeFloat(r);
                g = SanitizeFloat(g);
                b = SanitizeFloat(b);
                // scRGB 可为负（广色域溢出），截断；再按 SDR 白亮度归一化
                r = max(0.0f, r) / whiteScale;
                g = max(0.0f, g) / whiteScale;
                b = max(0.0f, b) / whiteScale;
                // 直接 sRGB 编码：与 SDR 路径观感一致，超过 1.0 的 HDR 高光裁剪为白
                r = LinearToSRGB(r);
                g = LinearToSRGB(g);
                b = LinearToSRGB(b);
                pDstRow[x * 4 + 0] = cb = static_cast<BYTE>(b * 255.0f + 0.5f);
                pDstRow[x * 4 + 1] = cg = static_cast<BYTE>(g * 255.0f + 0.5f);
                pDstRow[x * 4 + 2] = cbb = static_cast<BYTE>(r * 255.0f + 0.5f);
                pDstRow[x * 4 + 3] = 0xFF;
            }
            else if (hdrDesktop) {
                // HDR 桌面的 8-bit 帧 = OETF(原始 scRGB)：先解码回线性，再与 FP16 相同地归一化
                b = SRGBToLinear(pSrcRow[x * 4 + 0] / 255.0f) / whiteScale;
                g = SRGBToLinear(pSrcRow[x * 4 + 1] / 255.0f) / whiteScale;
                r = SRGBToLinear(pSrcRow[x * 4 + 2] / 255.0f) / whiteScale;
                b = LinearToSRGB(b);
                g = LinearToSRGB(g);
                r = LinearToSRGB(r);
                pDstRow[x * 4 + 0] = cb = static_cast<BYTE>(b * 255.0f + 0.5f);
                pDstRow[x * 4 + 1] = cg = static_cast<BYTE>(g * 255.0f + 0.5f);
                pDstRow[x * 4 + 2] = cbb = static_cast<BYTE>(r * 255.0f + 0.5f);
                pDstRow[x * 4 + 3] = 0xFF;
            }
            else {
                memcpy(pDstRow + x * 4, pSrcRow + x * 4, 4);
            }
            if (cb | cg | cbb) isBlack = false;
        }
    }

    BITMAPINFO bmi = { 0 };
    bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmi.bmiHeader.biWidth = w;
    bmi.bmiHeader.biHeight = -h;
    bmi.bmiHeader.biPlanes = 1;
    bmi.bmiHeader.biBitCount = 32;
    bmi.bmiHeader.biCompression = BI_RGB;
    hBitmap = CreateDIBitmap(hdc, &bmi.bmiHeader, CBM_INIT,
        bgraBuffer.data(), &bmi, DIB_RGB_COLORS);

    ReleaseDC(nullptr, hdc);
    g_pImmediateContext->Unmap(pStaging, 0);
    pStaging->Release();
    g_pDeskDupl->ReleaseFrame();   // 必须释放

    if (!hBitmap) return E_FAIL;
    isBlackOut = isBlack;
    hOutBitmap = hBitmap;
    return S_OK;
}

// ---------- 复制位图到剪贴板 ----------
void CopyBitmapToClipboard(HBITMAP hBitmap) {
    if (RetryOpenClipboard(g_hMainWnd, 5)) {
        EmptyClipboard();
        SetClipboardData(CF_BITMAP, hBitmap); // 剪贴板接管 hBitmap 的所有权
        CloseClipboard();
        ShowBalloonTip(L"QuickSnap", L"截图已复制到剪贴板");
    }
    else {
        DeleteObject(hBitmap);
        ShowBalloonTip(L"QuickSnap", L"剪贴板打开失败");
    }
}

// ---------- 后台重建捕获（静默，带模式切换缓冲等待） ----------
bool EnsureDuplication() {
    g_bNeedReinitDXGI = false;
    Sleep(100);  // 模式切换过渡期稍作等待，避免创建到过渡状态的捕获
    if (!InitDXGICapture(true)) {
        g_bNeedReinitDXGI = true;
        return false;
    }
    return true;
}

// ---------- 截屏复制到剪贴板 ----------
void CleanupDXGI();
void CaptureAndCopyToClipboard() {
    // 模式切换（HDR 开关）后 DWM 可能持续输出全黑帧零点几秒到几秒，
    // 前 6 次仅重新取帧，之后重建 duplication，仍全黑则提示且不污染剪贴板
    const int maxAttempts = 12;
    for (int attempt = 0; attempt < maxAttempts; attempt++) {
        // duplication 缺失或已标记失效：重建
        if (!g_pDeskDupl || g_bNeedReinitDXGI) {
            if (!EnsureDuplication()) return; // 本次失败，下次热键再试（不永久放弃）
            continue;
        }
        // 主动检测 HDR 开关 / 分辨率变化（避免拿到旧 duplication 的黑帧）
        if (CheckOutputChanged()) {
            OutputDebugString(L"QuickSnap: 检测到显示模式（HDR/SDR）变化，重建捕获\n");
            g_LastModeChangeTick = GetTickCount();
            CleanupDXGI();
            continue;
        }

        bool isBlack = false;
        HBITMAP hBitmap = nullptr;
        HRESULT hr = TryCaptureOnce(isBlack, hBitmap);

        if (hr == DXGI_ERROR_WAIT_TIMEOUT) {
            if (hBitmap) DeleteObject(hBitmap);
            return; // 屏幕无更新，不算失败
        }
        if (FAILED(hr)) {
            if (hBitmap) DeleteObject(hBitmap);
            g_LastModeChangeTick = GetTickCount();
            g_bNeedReinitDXGI = true;
            continue; // 重建后重试
        }

        if (isBlack && attempt < maxAttempts - 1) {
            OutputDebugString(L"QuickSnap: 捕获到全黑帧，重试\n");
            if (hBitmap) DeleteObject(hBitmap);
            if (attempt == 5) CleanupDXGI(); // 重取帧无效，改为重建 duplication
            Sleep(150);
            continue;
        }
        if (isBlack) {
            DeleteObject(hBitmap);
            ShowBalloonTip(L"QuickSnap", L"捕获到全黑画面（可能正在切换显示模式），请稍后重试");
            return;
        }

        CopyBitmapToClipboard(hBitmap);
        return;
    }
}

// ---------- 释放资源 ----------
void CleanupDXGI() {
    if (g_pDeskDupl) { g_pDeskDupl->Release(); g_pDeskDupl = nullptr; }
    if (g_pImmediateContext) { g_pImmediateContext->Release(); g_pImmediateContext = nullptr; }
    if (g_pD3DDevice) { g_pD3DDevice->Release(); g_pD3DDevice = nullptr; }
}

// ---------- 窗口过程 ----------
LRESULT CALLBACK WndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    switch (msg) {
    case WM_TRAYICON:
        if (lParam == WM_RBUTTONUP) {
            POINT pt;
            GetCursorPos(&pt);
            SetForegroundWindow(hWnd);
            UINT ret = TrackPopupMenu(g_hPopupMenu,
                TPM_RIGHTBUTTON | TPM_BOTTOMALIGN | TPM_RETURNCMD,
                pt.x, pt.y, 0, hWnd, nullptr);
            if (ret == MENU_EXIT) DestroyWindow(hWnd);
        }
        break;

    case WM_HOTKEY:
        if (wParam == HOTKEY_SCREENSHOT) {
            CaptureAndCopyToClipboard();
        }
        else if (wParam == HOTKEY_QUIT) {
            DestroyWindow(hWnd);
        }
        break;

    case WM_DISPLAYCHANGE:
        g_bNeedReinitDXGI = true;
        g_LastModeChangeTick = GetTickCount();
        break;

    case WM_DESTROY:
        UnregisterHotKey(hWnd, HOTKEY_SCREENSHOT);
        UnregisterHotKey(hWnd, HOTKEY_QUIT);
        Shell_NotifyIcon(NIM_DELETE, &m_nid);
        if (g_hPopupMenu) DestroyMenu(g_hPopupMenu);
        CleanupDXGI();
        PostQuitMessage(0);
        break;

    default:
        return DefWindowProc(hWnd, msg, wParam, lParam);
    }
    return 0;
}

// ---------- WinMain ----------
int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE hPrevInstance, LPSTR lpCmdLine, int nCmdShow) {
    SetProcessDpiAwareness(PROCESS_PER_MONITOR_DPI_AWARE);

    if (!InitDXGICapture()) {
        MessageBox(nullptr, L"DXGI 初始化失败！", L"错误", MB_OK);
        return -1;
    }

    WNDCLASSEX wc = { 0 };
    wc.cbSize = sizeof(WNDCLASSEX);
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInstance;
    wc.lpszClassName = L"QuickSnapClass";
    RegisterClassEx(&wc);

    g_hMainWnd = CreateWindowEx(0, wc.lpszClassName, L"QuickSnap", 0,
        CW_USEDEFAULT, CW_USEDEFAULT, 0, 0, HWND_MESSAGE, nullptr, hInstance, nullptr);
    if (!g_hMainWnd) {
        CleanupDXGI();
        return -1;
    }

    bool snapOK = false, quitOK = false;
    std::wstring snapKey = L"", quitKey = L"";

    if (RegisterHotKey(g_hMainWnd, HOTKEY_SCREENSHOT, MOD_CONTROL | MOD_ALT, 'X')) {
        snapOK = true; snapKey = L"Ctrl+Alt+X";
    }
    else if (RegisterHotKey(g_hMainWnd, HOTKEY_SCREENSHOT, MOD_CONTROL | MOD_SHIFT, 'X')) {
        snapOK = true; snapKey = L"Ctrl+Shift+X";
    }

    if (RegisterHotKey(g_hMainWnd, HOTKEY_QUIT, MOD_CONTROL | MOD_ALT, 'Q')) {
        quitOK = true; quitKey = L"Ctrl+Alt+Q";
    }
    else if (RegisterHotKey(g_hMainWnd, HOTKEY_QUIT, MOD_CONTROL | MOD_SHIFT, 'Q')) {
        quitOK = true; quitKey = L"Ctrl+Shift+Q";
    }

    ZeroMemory(&m_nid, sizeof(m_nid));
    m_nid.cbSize = sizeof(NOTIFYICONDATA);
    m_nid.hWnd = g_hMainWnd;
    m_nid.uFlags = NIF_MESSAGE | NIF_ICON | NIF_TIP;
    m_nid.uCallbackMessage = WM_TRAYICON;
    m_nid.hIcon = LoadIcon(nullptr, IDI_APPLICATION);
    wcscpy_s(m_nid.szTip, _countof(m_nid.szTip), L"QuickSnap");
    Shell_NotifyIcon(NIM_ADD, &m_nid);

    g_hPopupMenu = CreatePopupMenu();
    AppendMenu(g_hPopupMenu, MF_STRING, MENU_EXIT, L"退出");

    std::wstring startupTip = L"已启动 | ";
    startupTip += snapOK ? snapKey : L"截图热键失效";
    startupTip += L" | ";
    startupTip += quitOK ? quitKey : L"退出热键失效";
    ShowBalloonTip(L"QuickSnap", startupTip.c_str());

    // 调试模式：WindowsProject1.exe test 启动后自动截一次图
    if (lpCmdLine && strstr(lpCmdLine, "test")) {
        Sleep(1500);
        CaptureAndCopyToClipboard();
    }

    MSG msgLoop;
    while (GetMessage(&msgLoop, nullptr, 0, 0)) {
        TranslateMessage(&msgLoop);
        DispatchMessage(&msgLoop);
    }
    return (int)msgLoop.wParam;
}
