int main1(){
  int ebwm, omm, q1, w2s, b9, vb, ag, l, sk, oh;
  ebwm=1*2;
  omm=0;
  q1=0;
  w2s=4;
  b9=0;
  vb=ebwm;
  ag=omm;
  l=20;
  sk=0;
  oh=omm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b9 == omm;
  loop invariant (l == 20 + 3 * b9);
  loop invariant (vb == 2 + (b9 * (b9 + 1)) / 2);
  loop invariant 0 <= omm;
  loop invariant omm <= ebwm;
  loop invariant sk >= 0;
  loop invariant sk <= (ebwm - 1) * omm;
  loop invariant ebwm == 2;
  loop invariant 0 <= w2s;
  loop invariant 0 <= q1;
  loop invariant 0 <= oh;
  loop invariant ag == 23*omm + 3*omm*(omm+1)/2;
  loop invariant w2s <= 5;
  loop invariant (b9 == omm) &&
                   (w2s + 3*q1 == 4 + omm) &&
                   (0 <= omm && omm <= ebwm) &&
                   (ebwm == 2);
  loop assigns b9, w2s, q1, omm, sk, ag, vb, l, oh;
*/
while (1) {
      if (!(omm<ebwm)) {
          break;
      }
      b9 += 1;
      w2s += 1;
      if (w2s>=3) {
          w2s = w2s - 3;
          q1 = q1 + 1;
      }
      omm += 1;
      if (sk+1<ebwm) {
          sk = sk + omm;
      }
      ag = ag + 3;
      vb = vb + omm;
      l = l + 3;
      oh += vb;
      ag += l;
  }
}