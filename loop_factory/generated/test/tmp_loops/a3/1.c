int main1(int l){
  int po, e, m, p1y, fqv, s7, sw, si;

  po=l*5;
  e=po;
  m=1;
  p1y=1;
  fqv=1;
  s7=1;
  sw=l;
  si=e;

  while (fqv<=po) {
      m = m*(l/fqv);
      if ((fqv/2)%2==0) {
          s7 = 1;
      }
      else {
          s7 = -1;
      }
      fqv = fqv + 1;
      p1y = p1y+s7*m;
      m = m*(l/fqv);
      if ((e%2)==0) {
          si = sw*sw;
      }
      sw += s7;
      sw = sw*2+2;
      si = si*sw+2;
      si += l;
  }

}
