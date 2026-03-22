int main1(){
  int ota, l, qch, hv, vr;

  ota=60;
  l=ota;
  qch=1;
  hv=0;
  vr=(1%6)+2;

  while (1) {
      if (hv>=ota) {
          break;
      }
      hv = hv + 1;
      l = l*vr+1;
      qch = qch*vr;
      vr += l;
  }

}
