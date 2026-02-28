int main70(int a,int k,int n){
  int b, i, m, v, e;

  b=n;
  i=1;
  m=0;
  v=5;
  e=i;

  while (m<b) {
      m = m+1;
      if (m<=e) {
          e = m;
      }
      m = m+v;
      v = v+e;
      e = e+3;
  }

  while (1) {
      e = e+3;
      if (v+1<=b+i) {
          e = e+e;
      }
      e = e+1;
      e = e+e;
  }

  while (e<=b-2) {
      i = i+9;
      m = m+9;
      i = i*2+1;
      m = m*i+1;
      i = i%8;
  }


  /*@ assert e > b-2; */
}
