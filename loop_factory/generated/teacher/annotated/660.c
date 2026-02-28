int main1(int k,int p){
  int l, j, i, v, r, a;

  l=8;
  j=0;
  i=k;
  v=j;
  r=j;
  a=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == k;
  loop invariant p == \at(p, Pre);

  loop invariant v * i >= 0;
  loop invariant (i != 0) ==> (v / i >= 0);
  loop invariant i == \at(k, Pre);
  loop invariant l == 8;
  loop invariant k == \at(k, Pre);
  loop invariant (k >= 0) ==> (v >= 0);
  loop invariant (k <= 0) ==> (v <= 0);

  loop assigns v;
*/
while (1) {
      v = v+i;
  }

}
