int main1(){
  int o, svz1, r163, dgg;
  o=(1%60)+60;
  svz1=(1%9)+2;
  r163=0;
  dgg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 61 + r163 * ((svz1*(svz1-1))/2) + ((dgg*(dgg+1))/2);
  loop invariant 0 <= dgg;
  loop invariant dgg < svz1;
  loop invariant r163 >= 0;
  loop assigns dgg, r163, o;
*/
while (1) {
      if (o<=svz1*r163+dgg) {
          break;
      }
      if (dgg==svz1-1) {
          dgg = 0;
          r163++;
      }
      else {
          dgg = dgg + 1;
      }
      o = (dgg)+(o);
  }
}