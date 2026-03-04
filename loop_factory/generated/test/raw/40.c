int main1(int t){
  int sh, xv, x5x, lic;

  sh=(t%21)+7;
  xv=sh;
  x5x=(t%20)+5;
  lic=xv;

  while (1) {
      if (!(x5x>0)) {
          break;
      }
      x5x = x5x - 1;
      t += xv;
      lic += t;
  }

}
