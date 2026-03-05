int main1(){
  int a, em, y1, o4k;

  a=1+22;
  em=0;
  y1=0;
  o4k=0;

  while (em<a) {
      y1 += 1;
      o4k = o4k + 1;
      if (o4k>=4) {
          o4k -= 4;
          y1 += 1;
      }
      em = em + 1;
  }

}
