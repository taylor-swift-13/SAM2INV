int main1(int p,int q){
  int l, i, v, e;

  l=q;
  i=0;
  v=1;
  e=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant i >= 0;
  loop invariant e >= p;
  loop invariant i == 0;
  loop invariant l == \at(q, Pre);
  loop invariant e >= \at(p, Pre);

  loop invariant l == q;

  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (i < l/2) ==> 2*(v - 1) == (e - \at(p, Pre)) * (e + \at(p, Pre) + 11);
  loop invariant (i >= l/2) ==> 2*(v - 1) == 14*(e - \at(p, Pre));
  loop assigns v, e;
*/
while (i<l) {
      if (i<l/2) {
          v = v+e;
      }
      else {
          v = v+1;
      }
      v = v+5;
      e = e+1;
      if ((i%2)==0) {
          v = v+1;
      }
  }

}
