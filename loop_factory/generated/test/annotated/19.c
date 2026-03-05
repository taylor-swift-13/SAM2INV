int main1(int i){
  int tqbe;
  tqbe=-14684;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tqbe <= -5;
  loop invariant i <= \at(i, Pre);
  loop invariant i - 2 * tqbe <= \at(i, Pre) + 29368;
  loop assigns tqbe, i;
*/
while (tqbe<=-3) {
      tqbe = tqbe+tqbe-2;
      tqbe = tqbe + 3;
      i += tqbe;
  }
}