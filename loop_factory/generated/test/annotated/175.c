int main1(int a,int k,int p,int q){
  int l, i, v, y;

  l=23;
  i=l;
  v=a;
  y=k;

  /*>>> LOOP INVARIANT TO FILL <<<*/
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant y == k + (23 - i);
    loop invariant v == a + 2*k*(23 - i) + (23 - i)*(23 - i) + (27 - i)/7;
    loop invariant i >= 0;
    loop invariant i <= 23;
    loop invariant 0 <= i && i <= 23;
    loop invariant y >= k;
    loop invariant i + y == k + 23;

    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant q == \at(q,Pre);
    loop assigns v, i, y;
    loop variant i;
  */
  while (i>0) {
      v = v+y+y;
      v = v+1;
      y = y+1;
      if ((i%7)==0) {
          v = v+1;
      }
      i = i-1;
  }

}