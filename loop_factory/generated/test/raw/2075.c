int main1(){
  int rk, uz, b, baj;

  rk=69;
  uz=0;
  b=rk;
  baj=b;

  while (uz < rk) {
      uz += 1;
      if (b != baj) {
          baj = b;
      }
      b = b + uz;
  }

}
