int main1(int i){
  int bts8, iv, fe, s7g, rl, v4w;
  bts8=87;
  iv=-4;
  fe=33;
  s7g=0;
  rl=1;
  v4w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fe + s7g == 33;
  loop invariant iv - rl == -5;
  loop invariant 0 <= fe <= 33;
  loop invariant -4 <= iv <= bts8;
  loop invariant 0 <= v4w <= 33;
  loop assigns fe, s7g, iv, rl, v4w;
*/
while (fe>0&&iv<bts8) {
      if (fe<=rl) {
          v4w = fe;
      }
      else {
          v4w = rl;
      }
      fe = fe - v4w;
      s7g = s7g + v4w;
      iv++;
      rl = rl + 1;
  }
}