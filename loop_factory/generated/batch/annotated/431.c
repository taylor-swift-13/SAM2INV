int main1(int k,int p){
  int j, y, v, s;

  j=44;
  y=j;
  v=0;
  s=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant s <= v - 1;
  loop invariant y == 44;
  loop invariant j == 44;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant s >= v - 2;
  loop invariant ( (v == 0 && s == -2) || (v > 0 && s == v - 1) );
  loop invariant ( y == 44 );
  loop invariant ( j == 44 );
  loop invariant ( k == \at(k, Pre) );
  loop invariant ( p == \at(p, Pre) );
  loop invariant ( v >= 0 );
  loop invariant (v == 0 && s == -2) || (v > 0 && s == v - 1);
  loop assigns s, v;
*/
while (y-1>=0) {
      s = v;
      v = v+1;
  }

}
