int main1(int b){
  int h6, m, rzf, o0, bag6;
  h6=19;
  m=b;
  rzf=h6;
  o0=-8;
  bag6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre) + 2*bag6*bag6 - 6*bag6;
  loop invariant o0 == -8 + 4*bag6;
  loop invariant rzf == 2*bag6*bag6 - 10*bag6 + 19;
  loop invariant m == \at(b, Pre) + 19*bag6 + ((bag6-1)*bag6*(2*bag6-1))/3 - 5*bag6*(bag6-1);
  loop assigns b, bag6, o0, rzf, m;
*/
while (bag6<=h6) {
      m += rzf;
      rzf = rzf + o0;
      bag6++;
      o0 += 4;
      b = b + o0;
  }
}