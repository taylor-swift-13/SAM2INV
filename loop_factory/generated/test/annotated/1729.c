int main1(int v){
  int y, m, i;
  y=(v%28)+14;
  m=0;
  i=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 4*m;
  loop invariant y == (\at(v,Pre) % 28) + 14;
  loop invariant 0 <= m;
  loop invariant 2*v == 2*\at(v, Pre) + m*(m+1);
  loop assigns i, m, v;
*/
while (1) {
      if (!(m < y)) {
          break;
      }
      m++;
      i = i + 3;
      v = v + m;
      i = i + 1;
  }
}