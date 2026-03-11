int main1(int k){
  int i, ur, ldo, aud, za;

  i=54;
  ur=0;
  ldo=0;
  aud=0;
  za=i;

  while (ldo<i) {
      aud = aud + ldo;
      za = za + ur;
      ldo++;
  }

  while (aud<za) {
      aud += 1;
  }

}
