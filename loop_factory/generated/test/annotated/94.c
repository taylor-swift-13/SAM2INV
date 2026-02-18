int main1(int a,int n,int p,int q){
  int l, i, v, u;

  l=p;
  i=0;
  v=6;
  u=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@

    loop invariant l == p;
    loop invariant p == \at(p, Pre);

    loop invariant u <= 4;
    loop invariant i == 0;
    loop invariant p == \at(p,Pre);

    loop invariant (i >= l/2) ==> v + 2*u == 14;
    loop invariant l == \at(p, Pre);
    loop invariant (l > 0) ==> (i < l);

    loop assigns v, u;
  */
  while (i<l) {
      if (i<l/2) {
          v = v+u;
      }
      else {
          v = v+1;
      }
      v = v+1;
      u = u-1;
  }

}