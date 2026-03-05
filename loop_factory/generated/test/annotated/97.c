int main1(int p,int o){
  int y1, n5, w;
  y1=o-2;
  n5=0;
  w=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == \at(o, Pre);
  loop invariant y1 == \at(o, Pre) - 2;
  loop invariant w == 7 + 4 * n5 && n5 >= 0 && (n5 <= y1 || n5 == 0);
  loop invariant p == \at(p, Pre);
  loop assigns w, n5;
*/
while (n5<y1) {
      w += 4;
      n5++;
  }
}