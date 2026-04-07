int main1(){
  int qls, zy, hg9, b, ax, qkmr;
  qls=1;
  zy=0;
  hg9=qls;
  b=zy;
  ax=1;
  qkmr=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 0;
  loop invariant qkmr == -6 + ((hg9 - 1) * (hg9 + 2)) / 2;
  loop invariant 1 <= hg9;
  loop invariant hg9 <= qls + 1;
  loop invariant ax == 1;
  loop assigns b, ax, hg9, qkmr;
*/
while (hg9<=qls) {
      b = b*hg9;
      if (hg9<qls) {
          ax = ax*hg9;
      }
      hg9 = hg9 + 1;
      qkmr += hg9;
  }
}