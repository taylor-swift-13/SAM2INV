int main1(int f){
  int g7, a1, s2sk, bhw;
  g7=f+14;
  a1=0;
  s2sk=0;
  bhw=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g7 == f + 14;
  loop invariant (a1 == 0) ==> (s2sk == 0);
  loop invariant (a1 == 0) ==> (bhw == 2);
  loop invariant (a1 == 0) || (a1 == g7);
  loop invariant (a1 != 0) ==> (s2sk == f);
  loop invariant (a1 != 0) ==> (bhw == 2 + g7);
  loop assigns a1, bhw, s2sk;
*/
while (a1 < g7) {
      s2sk += f;
      bhw += g7;
      a1 = g7;
  }
}