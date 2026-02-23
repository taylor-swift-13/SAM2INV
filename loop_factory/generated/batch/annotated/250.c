int main1(int b,int p){
  int i, l, v;

  i=b;
  l=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == b;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l >= 0;
  loop invariant v >= -1;
  loop invariant v <= l - 1;

  loop invariant v == l - 1;
  loop invariant (b >= 0) ==> (v == l - 1);

  loop invariant (b + i) < 0 ==> (v == -1);
  loop invariant ((b + i) >= 0 && l <= b + i) ==> (v == -1 + l);
  loop invariant ((b + i) >= 0 && l >  b + i) ==> (v == -1 + (b + i));
  loop invariant 0 <= l;
  loop invariant -1 <= v;
  loop assigns l, v;
*/
while (l+1<=i) {
      if (l+1<=b+i) {
          v = v+1;
      }
      l = l+1;
  }

}
