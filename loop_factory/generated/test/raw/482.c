int main1(int n,int m){
  int r4, xfz, hk, f62, v0, t38p, e6;

  r4=m;
  xfz=1;
  hk=0;
  f62=(n%28)+10;
  v0=m;
  t38p=n;
  e6=0;

  while (f62>hk) {
      f62 = f62 - hk;
      hk++;
      v0 = v0+r4-xfz;
      t38p = t38p+(hk%2);
      n = n + 3;
  }

  while (f62>0) {
      t38p = t38p+n*n;
      xfz = xfz+m*m;
      f62 = f62 - 1;
      hk = hk+n*m;
      e6 += xfz;
  }

}
