int main1(int k){
  int ur, v945, lv, lc;
  ur=46;
  v945=1;
  lv=5;
  lc=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lv == 5 + (v945 - 1) * (v945 - 1);
  loop invariant lc == 3 + 5 * (v945 - 1) + ((v945 - 1) * v945 * (2 * v945 - 1)) / 6;
  loop invariant 1 <= v945 <= ur + 1;
  loop assigns lv, lc, v945;
*/
while (v945<=ur) {
      lv = lv+2*v945-1;
      lc += lv;
      v945++;
  }
}