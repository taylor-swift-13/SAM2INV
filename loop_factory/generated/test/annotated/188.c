int main1(int b,int y){
  int yo2, ju, ebi, zh;
  yo2=11;
  ju=0;
  ebi=y;
  zh=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((zh == 3 && ebi == y) || (ebi == zh*zh));
  loop invariant ( b >= \at(b, Pre) );
  loop invariant ( y == \at(y, Pre) );
  loop invariant ( zh >= 3 );
  loop invariant ju == 0;
  loop invariant yo2 == 11;
  loop assigns zh, ebi, b;
*/
while (ju+5<=yo2) {
      zh++;
      ebi = zh*zh;
      b += ebi;
  }
}