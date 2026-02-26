int main1(int b,int p){
  int i, l, v;

  i=b;
  l=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant v >= -1;
  loop invariant (l <= i + b) ==> (v == -1 + 4*l + (l*(l-1))/2);
  loop invariant i == b;
  loop invariant l >= 0;
  loop invariant (i < 0) ==> (l == 0) && (i >= 0) ==> (l <= i) && (v >= -1);

  loop invariant b == \at(b, Pre);
  loop invariant v >= -1 + (l*(l-1))/2;
  loop invariant v <= -1 + (l*l + 7*l)/2;
  loop invariant ((v + 1) - (l*(l-1))/2) % 4 == 0;
  loop invariant 0 <= l;
  loop invariant v >= -1 + l*(l-1)/2;
  loop invariant p == \at(p, Pre);

  loop assigns v, l;
*/
while (l+1<=i) {
      if (l+1<=b+i) {
          v = v+4;
      }
      v = v+l;
      l = l+1;
  }

}
