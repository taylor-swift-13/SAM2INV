int main1(int o,int v){
  int js, eoz, um63, sa6;
  js=o+16;
  eoz=0;
  um63=0;
  sa6=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == \at(o, Pre) + um63 * js;
  loop invariant eoz == 0;
  loop invariant um63 >= 0;
  loop invariant (um63 == 0) ==> sa6 == v;
  loop invariant (um63 > 0) ==> sa6 == js - (um63 - 1);
  loop invariant v == \at(v, Pre);
  loop invariant js == \at(o, Pre) + 16;
  loop assigns o, sa6, um63;
*/
while (eoz<=js-2) {
      sa6 = js-um63;
      um63++;
      o = o + js;
  }
}