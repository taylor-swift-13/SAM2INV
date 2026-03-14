int main1(int z){
  int za, ni, q, vy, p, g;

  za=z+23;
  ni=0;
  q=0;
  vy=0;
  p=0;
  g=7;

  for (; ni<za; ni += 1) {
      vy = ni%5;
      if (!(!(ni>=g))) {
          p = (ni-g)%5;
          q = q+vy-p;
      }
      else {
          q = q + vy;
      }
      g = g + vy;
  }

}
