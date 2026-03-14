int main1(){
  int ue, m, b, ls, g9;
  ue=169;
  m=2;
  b=0;
  ls=0;
  g9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g9 >= 0;
  loop invariant b == g9 / 2;
  loop invariant m <= ue;
  loop invariant ls == (m - 2) % 2;
  loop invariant m == 2 + g9;
  loop assigns m, g9, ls, b;
*/
for (; m<=ue-1; m++) {
      g9++;
      ls++;
      if (ls>=2) {
          ls -= 2;
          b += 1;
      }
  }
}