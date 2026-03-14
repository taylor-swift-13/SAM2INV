int main1(int w,int p){
  int qg, s, xc, tt;

  qg=w+25;
  s=0;
  xc=s;
  tt=0;

  while (1) {
      tt -= 1;
      xc = xc + 1;
      w = w + s;
      s++;
      if (s>=qg) {
          break;
      }
  }

}
