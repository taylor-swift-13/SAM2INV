int main1(){
  int nn1, nd5z, swkr;

  nn1=1;
  nd5z=0;
  swkr=0;

  while (nd5z < nn1) {
      swkr = swkr + ((nd5z++ * 2 < nn1) ? 1 : -1);
      nd5z = nn1;
  }

}
