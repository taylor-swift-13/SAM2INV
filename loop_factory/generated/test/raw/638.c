int main1(int e){
  int k, vst, f5k, zua, s7, qx;

  k=(e%13)+15;
  vst=1;
  f5k=0;
  zua=0;
  s7=0;
  qx=5;

  while (1) {
      if (!(vst<k)) {
          break;
      }
      zua = vst%5;
      if (vst>=qx) {
          s7 = (vst-qx)%5;
          f5k = f5k+zua-s7;
      }
      else {
          f5k += zua;
      }
      qx += s7;
      vst++;
  }

}
