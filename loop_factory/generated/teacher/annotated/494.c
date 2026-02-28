int main1(int b,int p){
  int l, i, y, q;

  l=b+19;
  i=0;
  y=p;
  q=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == b + 19;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (y - p) % 3 == 0;
  loop invariant y >= p;
  loop invariant l == \at(b, Pre) + 19;
  loop invariant y >= \at(p, Pre);
  loop invariant (y - \at(p, Pre)) % 3 == 0;
  loop invariant ( (y - \at(p,Pre)) % 3 == 0 );
  loop invariant ( (q == y - 3) || ( (y == \at(p,Pre)) && ( q == \at(b,Pre) ) ) );
  loop invariant ( b == \at(b,Pre) );
  loop invariant ( p == \at(p,Pre) );
  loop assigns q, y;
*/
while (1) {
      q = y;
      y = y+2;
      y = y+1;
  }

}
