int main1(int v){
  int nd5, r, xbp, pbi;

  nd5=0;
  r=12;
  xbp=0;
  pbi=(v%35)+8;

  while (1) {
      if (!(pbi>0)) {
          break;
      }
      xbp = xbp+pbi*pbi;
      nd5 = nd5+r*r;
      r = r+pbi*pbi;
      v = (xbp)+(v);
      pbi--;
  }

}
