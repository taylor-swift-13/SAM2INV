int main1(int a,int m,int p){
  int l, v, i, k, h, s;

  l=23;
  v=0;
  i=0;
  k=0;
  h=l;
  s=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= l;
  loop invariant (i <= l/2) ==> k == 2*i;
  loop invariant (i > l/2) ==> k == 2*(l - 1) - 2*i;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (i < l/2) ==> (k == 2*i);
  loop invariant (i >= l/2) ==> (k == 2*(l - 1 - i));
  loop invariant 0 <= i <= l;
  loop invariant (i <= l/2) ==> (k == 2*i);
  loop invariant l == 23;
  loop invariant i >= 0;
  loop invariant k <= 2*i;
  loop invariant 0 <= i;
  loop assigns i, k;
*/
while (i<l) {
      if (i<l/2) {
          k = k+2;
      }
      else {
          k = k-2;
      }
      i = i+1;
  }

}
