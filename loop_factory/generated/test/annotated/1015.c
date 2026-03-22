int main1(){
  int oi, v7l, pc7, s, kg1, lgx;
  oi=68;
  v7l=3;
  pc7=0;
  s=0;
  kg1=0;
  lgx=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= s <= 4;
  loop invariant 0 <= kg1 <= 4;
  loop invariant -4*(v7l - 3) <= pc7 <= 4*(v7l - 3);
  loop invariant oi == 68;
  loop invariant 6 <= lgx;
  loop invariant lgx <= 6 + 4*(v7l - 3);
  loop invariant 3 <= v7l <= oi;
  loop assigns s, kg1, pc7, v7l, lgx;
*/
while (v7l<oi) {
      s = v7l%5;
      if (!(!(v7l>=lgx))) {
          kg1 = (v7l-lgx)%5;
          pc7 = pc7+s-kg1;
      }
      else {
          pc7 = pc7 + s;
      }
      v7l += 1;
      lgx = lgx + kg1;
  }
}