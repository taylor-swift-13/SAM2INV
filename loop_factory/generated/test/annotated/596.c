int main1(int u,int q){
  int vots, w, ooe;
  vots=1;
  w=(q%20)+10;
  ooe=(q%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == ((\at(q, Pre) % 20) + 10) - ((vots - 1) / 2) &&
                    ooe == ((\at(q, Pre) % 15) + 8) - (vots / 2);
  loop invariant vots >= 1;
  loop invariant w + ooe + vots == ((\at(q,Pre) % 20) + 10) + ((\at(q,Pre) % 15) + 8) + 1;
  loop invariant w + ooe == (q % 20 + 10) + (q % 15 + 8) - (vots - 1);
  loop assigns w, ooe, vots;
*/
while (1) {
      if (!(w>0&&ooe>0)) {
          break;
      }
      if (!(!(vots%2==0))) {
          w = w - 1;
      }
      else {
          ooe = ooe - 1;
      }
      vots++;
  }
}