int main1(int w){
  int z, qf, q, x7s, t, klj, n;

  z=(w%17)+15;
  qf=z;
  q=0;
  x7s=0;
  t=0;
  klj=(w%18)+5;
  n=qf;

  while (klj>=1) {
      t = t+w*w;
      x7s = x7s+w*w;
      n += z;
      klj--;
      q = q+w*w;
  }

  for (; n>1; n = n/2) {
  }

}
