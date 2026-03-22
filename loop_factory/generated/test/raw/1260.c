int main1(){
  int aiao, b9q, or, b2, qb, pk, c6;

  aiao=1+3;
  b9q=0;
  or=aiao;
  b2=2;
  qb=b9q;
  pk=(1%6)+2;
  c6=b9q;

  while (1) {
      if (qb>=aiao) {
          break;
      }
      qb++;
      or = or*pk+1;
      b2 = b2*pk;
      pk += b9q;
      pk = pk*4;
      c6 = c6/4;
  }

}
