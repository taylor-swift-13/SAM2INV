int main1(int o,int f){
  int q6, c, r6i, ck, hnr;
  q6=o;
  c=q6;
  r6i=0;
  ck=0;
  hnr=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == o + r6i;
  loop invariant r6i >= 0;
  loop invariant hnr == -3 + 3*r6i;
  loop invariant ck == r6i*(r6i+1)/2;
  loop invariant f == \at(f,Pre) + r6i*(r6i+1)/2;
  loop invariant r6i == c - \at(o,Pre);
  loop invariant c >= \at(o,Pre);
  loop invariant q6 == o;
  loop assigns r6i, f, hnr, ck, c;
*/
while (1) {
      if (!(c-4>=0)) {
          break;
      }
      r6i = r6i + 1;
      f = f + r6i;
      hnr = hnr + 3;
      ck = ck + r6i;
      c = c + 1;
  }
}