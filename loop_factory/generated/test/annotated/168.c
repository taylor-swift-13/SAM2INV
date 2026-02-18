int main1(int k,int m,int n,int p){
  int l, i, v;

  l=k+11;
  i=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == k + 11;
    loop invariant 0 <= i;


    loop invariant (l < 0) || (i <= l);

    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);

    loop invariant l == \at(k, Pre) + 11;
    loop invariant i >= 0;
    loop invariant (i == 0) ==> (v == \at(k, Pre));
    loop assigns i, v;
  */
  while (i<l) {
      v = v+v;
      v = v+1;
      if ((i%2)==0) {
          v = v+2;
      }
      i = i+1;
  }

}