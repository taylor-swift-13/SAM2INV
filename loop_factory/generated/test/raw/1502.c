int main1(){
  int es, bt9, d, pb, o1;

  es=5;
  bt9=0;
  d=bt9;
  pb=es;
  o1=13;

  while (bt9 < es) {
      bt9++;
      d = d * o1;
      pb = pb * o1;
      o1 = o1*2+(d%4)+0;
  }

}
