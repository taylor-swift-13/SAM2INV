int main1(){
  int ne1, go7, fg7, m, l0t;
  ne1=60;
  go7=1;
  fg7=0;
  m=0;
  l0t=go7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l0t == 1 + (ne1 - go7) * fg7;
  loop invariant m + fg7 <= ne1;
  loop invariant 0 <= fg7;
  loop invariant fg7 <= ne1;
  loop invariant 0 <= m <= ne1;
  loop invariant go7 == 1;
  loop assigns fg7, m, l0t;
*/
while (fg7<ne1) {
      fg7 += 1;
      m = ne1-fg7;
      l0t = l0t+ne1-go7;
  }
}