int main7(int k,int n,int p){
  int l, u, f, d, a;

  l=k;
  u=l;
  f=k;
  d=-8;
  a=k;

  while (u>0) {
      if (a<l) {
          d = f;
      }
      f = f+1;
      f = f+d;
      d = d+a;
      a = a+5;
  }

  while (f>0) {
      u = u+3;
      while (a+4<=f) {
          d = f-l;
          l = l+1;
          l = l*2+1;
          d = d*l+1;
          l = l%6;
      }
  }


  /*@ assert a+4 > f; */
}
