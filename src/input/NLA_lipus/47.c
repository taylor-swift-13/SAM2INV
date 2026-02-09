/*@ requires x >= 0 && y >= 1;*/
int main1(){

  int x, y, q, a, b;
  
  q = 0;
  a = 0;
  b = x;

  while(b != 0) {
        if (a + 1 == y) {
            q = q + 1;
            a = 0;
            b = b - 1;
        }
        else {
            a = a + 1;
            b = b - 1;
        }
    }
  /*@ assert q == x / y;*/
}

