int main117(int z,int g,int e){
  int szy, lq1, hu, ci, wp, sig;

  szy=g;
  lq1=(g%40)+2;
  hu=0;
  ci=0;
  wp=g;
  sig=0;

  while (lq1!=hu) {
      hu = lq1;
      lq1 = (lq1+szy/lq1)/2;
      sig += lq1;
      wp = wp+lq1-hu;
      g += lq1;
      ci = ci + wp;
  }

  while (1) {
      if (sig+2<=wp) {
          sig += 2;
      }
      else {
          sig = wp;
      }
      g = g+sig-sig;
      z += 1;
      g -= 1;
      szy++;
      if (szy>=wp) {
          break;
      }
  }

}
