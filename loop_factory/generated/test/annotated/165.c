int main1(int a,int b,int n,int p){
  int l, i, v;

  l=67;
  i=0;
  v=0;

  
  /*@

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == 0);

    loop invariant (i > 0) ==> (v == n);

    loop invariant l == 67;

    loop invariant n == \at(n, Pre);

    loop invariant a == \at(a, Pre);

    loop invariant 0 <= i && i <= l;

    loop invariant 0 <= i;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant i == 0 ==> v == 0;

    loop invariant i > 0 ==> v == n;

    loop invariant b == \at(b, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns v, i;

  */
  while (i<l) {
      v = n;
      i = i+1;
  }

}