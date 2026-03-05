int main104(int t,int f){
  int yz, um, e, g, ig, xa;

  yz=f+15;
  um=0;
  e=0;
  g=0;
  ig=7;
  xa=(f%20)+5;

  while (e<yz) {
      um = (um+1)%4;
      e += 1;
      g = g + e;
      f += um;
      ig = ig + 3;
      g = g + 3;
  }

  while (1) {
      if (!(xa>=1)) {
          break;
      }
      xa -= 1;
      t = t + 3;
      f = f + xa;
      t = t + 5;
      f += t;
  }

}
