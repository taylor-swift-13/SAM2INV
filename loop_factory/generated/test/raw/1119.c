int main1(int i){
  int k, ga, fogf, w;

  k=54;
  ga=0;
  fogf=0;
  w=-8;

  while (fogf<k) {
      ga = ga + i;
      fogf++;
      w += fogf;
  }

  while (1) {
      if (!(ga>=2)) {
          break;
      }
      w = w+fogf*ga;
      fogf = fogf+(w%6);
      ga = 1;
  }

}
