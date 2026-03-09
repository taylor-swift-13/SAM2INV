int main1(){
  int oh37, x, um, ad, ici;
  oh37=58;
  x=0;
  um=1;
  ad=0;
  ici=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ad >= 0;
  loop invariant oh37 == 58;
  loop invariant x == 0;
  loop invariant ici == 2*um - 7;
  loop assigns ad, um, ici;
*/
while (um<oh37) {
      ad += 1;
      um = 2*um;
      ici += um;
      ici += x;
  }
}