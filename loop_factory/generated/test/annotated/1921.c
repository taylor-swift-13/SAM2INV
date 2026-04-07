int main1(int v){
  int yo9i, fw, js, z0q, v3, x, ek, o;
  yo9i=38;
  fw=0;
  js=5;
  z0q=0;
  v3=0;
  x=13;
  ek=2;
  o=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= fw;
  loop invariant fw <= yo9i;
  loop invariant v3 == fw;
  loop invariant (x + fw) == 13;
  loop invariant (js + z0q) == 5;
  loop invariant 0 <= js;
  loop invariant 0 <= z0q;
  loop invariant 2 <= ek;
  loop invariant ek <= (2 + 5*fw);
  loop invariant 2*(o - \at(v, Pre)) == (fw*(fw + 7));
  loop invariant o >= v + 4*fw;
  loop assigns js, z0q, o, v3, fw, x, ek;
*/
while (1) {
      if (!(fw<yo9i)) {
          break;
      }
      if (!(!(fw%2==0))) {
          if (js>0) {
              js = js - 1;
              z0q++;
          }
      }
      else {
          if (z0q>0) {
              z0q -= 1;
              js += 1;
          }
      }
      o = o + 3;
      v3++;
      fw += 1;
      x--;
      ek = ek + js;
      o = o + fw;
  }
}