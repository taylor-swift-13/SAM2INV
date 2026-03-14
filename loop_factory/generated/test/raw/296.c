int main1(){
  int drf, b, g, h;

  drf=15;
  b=0;
  g=0;
  h=-2;

  while (g<drf) {
      h = drf-g;
      h -= h;
      g += 4;
  }

  for (; b<=h-1; b += 1) {
      g = g + 5;
      if (b+3<=h+h) {
          g++;
      }
  }

}
