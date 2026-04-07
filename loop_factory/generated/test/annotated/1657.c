int main1(int w){
  int y1, sc, ikb, zh;
  y1=62;
  sc=0;
  ikb=-6;
  zh=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ikb - zh == -12;
  loop invariant ikb == -6 + sc * w;
  loop invariant 0 <= sc;
  loop invariant sc <= y1;
  loop assigns sc, ikb, zh;
*/
while (sc < y1) {
      sc++;
      zh = zh + w;
      ikb = ikb + w;
  }
}