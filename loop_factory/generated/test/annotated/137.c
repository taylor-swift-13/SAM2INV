int main1(int a,int b,int p,int q){
  int l, i, v, j, e;

  l=10;
  i=0;
  v=i;
  j=q;
  e=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant e == a + i*(i+1)/2;
    loop invariant j == q + 6*i + i*(i-1)/2;

    loop invariant a == \at(a, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant e == \at(a, Pre) + i*(i+1)/2;
    loop invariant j == \at(q, Pre) + 6*i + i*(i-1)/2;
    loop invariant a == \at(a, Pre) && q == \at(q, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant l == 10;
    loop invariant j == \at(q, Pre) + i*(i+11)/2;

    loop invariant (i == 0) ==> (v == 0 && e == a && j == q);
    loop invariant b == \at(b, Pre);
    loop assigns v, e, j, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+j+e;
      v = v+1;
      if ((i%5)==0) {
          v = v+1;
      }
      e = e+i;
      j = j+6;
      e = e+1;
      j = j+i;
      i = i+1;
  }

}