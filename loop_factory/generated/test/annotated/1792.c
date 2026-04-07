int main1(int a){
  int hnk, n, ud, eb, y;
  hnk=a*5;
  n=-3;
  ud=0;
  eb=hnk;
  y=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ( (n == -3) ==> (eb == hnk) );
  loop invariant ( (n == hnk) ==> (eb == hnk / 2) );
  loop invariant ( (n == -3) ==> (y == 8) );
  loop invariant ( ud == 0 );
  loop invariant hnk == 5 * a;
  loop invariant n == -3 || n == hnk;
  loop invariant y >= 8;
  loop invariant hnk == \at(a, Pre) * 5;
  loop invariant ((y >= 8) && (y <= 9));
  loop assigns eb, y, ud, n;
*/
while (n<=hnk-1) {
      eb = eb/2;
      y++;
      ud = ud*2;
      n = hnk;
  }
}