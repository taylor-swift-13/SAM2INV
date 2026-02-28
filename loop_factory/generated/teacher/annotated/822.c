int main1(int m,int p){
  int o, g, v;

  o=13;
  g=2;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -8 || v == 0;
  loop invariant g == 2;
  loop invariant o == 13;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v <= 0;
  loop invariant -8 <= v <= 6;
  loop invariant (o == 13);
  loop invariant (g == 2);
  loop invariant (m == \at(m, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant ((v == -8) || (v == 0));
  loop invariant (g <= o);
  loop assigns v;
*/
while (g+1<=o) {
      v = v+3;
      if (v+7<o) {
          v = v-v;
      }
  }

}
