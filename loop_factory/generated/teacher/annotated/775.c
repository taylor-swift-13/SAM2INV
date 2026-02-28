int main1(int a,int k){
  int o, v, y, s;

  o=a-2;
  v=1;
  y=0;
  s=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == a - 2;
  loop invariant (y == 0) ==> (s == 1);
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant y >= 0;
  loop invariant ( (y == 0) ==> (s == 1) ) && ( (y > 0) ==> (s == 2*o - y + 2) );
  loop invariant y == 0 ==> s == 1;
  loop invariant ((y == 0) && (s == 1)) || ((y > 0) && (s == 2*o - y + 2));
  loop invariant ((y == 0 && s == 1) || (s == 2 * o - y + 2));
  loop assigns s, y;
*/
while (1) {
      s = o-y;
      y = y+1;
      s = s+s;
      s = s+y;
  }

}
