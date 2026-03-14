int main1(int k){
  int xvn, r2zv, zgvm, l6dn, j8, w3, e7;

  xvn=(k%34)+9;
  r2zv=0;
  zgvm=5;
  l6dn=xvn;
  j8=xvn;
  w3=r2zv;
  e7=xvn;

  while (r2zv<xvn) {
      zgvm = zgvm + 9;
      l6dn += zgvm;
      j8 += l6dn;
      e7 = e7+xvn-r2zv;
      w3 += j8;
      r2zv = xvn;
  }

}
