int main1(){
  int a9, z, d, abd, ld;

  a9=1+8;
  z=0;
  d=0;
  abd=a9;
  ld=a9;

  while (d<a9) {
      abd = d+1;
      ld += a9;
      d += 2;
  }

  while (z+8<=d) {
      if (z%2==0) {
          ld += a9;
      }
      else {
          ld = ld+a9+1;
      }
      d = ((z+8))+(-(1));
  }

}
