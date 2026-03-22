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
