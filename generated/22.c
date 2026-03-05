int main22(int n,int z,int f){
  int ho, cxz, ccf, m9, ua, c51, kg7, hn4r;

  ho=121;
  cxz=ho;
  ccf=2;
  m9=0;
  ua=2;
  c51=ho;
  kg7=z;
  hn4r=n;

  while (cxz>1) {
      m9 = ccf+9;
      hn4r = hn4r + cxz;
      ccf = ccf + 1;
      c51 = c51 + 3;
      z = z+(ccf%6);
      f = f+(m9%4);
  }

  while (ho<ccf) {
      f += 2;
      cxz += n;
      ho += 1;
      kg7 += hn4r;
      kg7++;
      n = n + kg7;
  }

  while (cxz>0&&c51>0) {
      if (ho%2==0) {
          cxz = cxz - 1;
      }
      else {
          c51--;
      }
      ua = ua + cxz;
      ho += 1;
      n = n + c51;
      z = z*z+ua;
  }

}
